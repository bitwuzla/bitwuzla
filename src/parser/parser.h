/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_H_INCLUDED
#define BZLA_PARSER_H_INCLUDED

#include <bitwuzla/cpp/bitwuzla.h>

#include <fstream>

#include "api/checks.h"
#include "util/logger.h"
#include "util/statistics.h"

namespace bzla {
namespace parser {

class Parser
{
 public:
  /**
   * Constructor.
   * @param options  The associated Bitwuzla options. Parser creates Bitwuzla
   *                 instance from these options.
   * @param out      The output stream.
   * @note It is not safe to reuse a parser instance after a parse error.
   *       Subsequent parse queries after a parse error will return with
   *       an error.
   */
  Parser(bitwuzla::TermManager& tm,
         bitwuzla::Options& options,
         std::ostream* out = &std::cout)
      : d_options_orig(options),
        d_options(options),
        d_tm(tm),
        d_log_level(options.get(bitwuzla::Option::LOGLEVEL)),
        d_verbosity(options.get(bitwuzla::Option::VERBOSITY)),
        d_logger(d_log_level, d_verbosity),
        d_out(out)
  {
  }

  /** Destructor. */
  virtual ~Parser() {}

  /**
   * Enable or disable the automatic printing of the model after each
   * satisfiable query.
   *
   * Set to true to automatically print the model after every sat query. Must
   * be enabled to automatically print models for BTOR2 input (does not provide
   * a command to print the model like `(get-model)` in SMT-LIB2).
   * False (default) configures the standard behavior for SMT-LIB2 input (print
   * model only after a `(get-model)` command).
   *
   * @note By default, auto printing of the model is disabled.
   *
   * @param value True to enable auto printing of the model.
   */
  void configure_auto_print_model(bool value) { d_auto_print_model = value; }

  /**
   * Parse input, either from a file or from a string.
   * @param input      The name of the input file if `parse_file` is true,
   *                   else a string with the input.
   * @param parse_only True to only parse without executing check-sat calls.
   * @param parse_file True to parse an input file with the given name `input`,
   *                   false to parse from `input` as a string input.
   * @return False on error. The error message can be queried via `error_msg()`.
   */
  virtual bool parse(const std::string& input,
                     bool parse_only,
                     bool parse_file) = 0;
  /**
   * Parse input.
   * @param infile_name The name of the input file. This is required for error
   *                    message printing only. Use '<stdin>' if the input
   *                    stream is std::cin, and '<string>' if the input stream
   *                    was created from a string.
   * @param inpur       The input stream.
   * @param parse_only  True to only parse without executing check-sat calls.
   * @return False on error. The error message can be queried via `error_msg()`.
   */
  virtual bool parse(const std::string& infile_name,
                     std::istream& input,
                     bool parse_only) = 0;

  /**
   * Parse term from string.
   * @param input The input string.
   * @return The parsed term.
   */
  virtual bool parse_term(const std::string& input, bitwuzla::Term& res) = 0;
  /**
   * Parse sort from string.
   * @param input The input string.
   * @return The parsed sort.
   */
  virtual bool parse_sort(const std::string& input, bitwuzla::Sort& res) = 0;
  /**
   * Get the current set of (user-)declared sort symbols.
   * @note Corresponds to the sorts declared via SMT-LIB command `declare-sort`.
   *       Will always return an empty set for BTOR2 input.
   * @return The declared sorts.
   */
  virtual std::vector<bitwuzla::Sort> get_declared_sorts() const = 0;
  /**
   * Get the current set of (user-)declared function symbols.
   * @note Corresponds to the function symbols declared via SMT-LIB commands
   *       `declare-const` and `declare-fun`.
   * @return The declared function symbols.
   */
  virtual std::vector<bitwuzla::Term> get_declared_funs() const = 0;

  /** Configure Bitwuzla terminator.
   * @param terminator The terminator to configure as terminator for Bitwuzla.
   */
  void configure_terminator(bitwuzla::Terminator* terminator)
  {
    if (d_bitwuzla)
    {
      d_bitwuzla->configure_terminator(terminator);
    }
    d_terminator = terminator;
  }

  /** @return The Bitwuzla instance. */
  std::shared_ptr<bitwuzla::Bitwuzla> bitwuzla() { return d_bitwuzla; }

  /** @return The error message. */
  const std::string& error_msg() { return d_error; }

 protected:
  /** Initialize Bitwuzla instance. */
  void init_bitwuzla()
  {
    if (!d_bitwuzla)
    {
      d_bitwuzla.reset(new bitwuzla::Bitwuzla(d_tm, d_options));
    }
  }
  /**
   * Determine if the parser is required (by the Bitwuzla terminator) to
   * terminate.
   * @return True if parser is required to terminate.
   */
  bool terminate()
  {
    return d_terminator != nullptr && d_terminator->terminate();
  }

  /** The original Bitwuzla configuration options. */
  bitwuzla::Options& d_options_orig;
  /** The Bitwuzla configuration options. */
  bitwuzla::Options d_options;
  /** The associated term manager instance. */
  bitwuzla::TermManager& d_tm;
  /** The Bitwuzla instance. */
  std::shared_ptr<bitwuzla::Bitwuzla> d_bitwuzla = nullptr;
  /** The Bitwuzla terminator. */
  bitwuzla::Terminator* d_terminator = nullptr;

  std::istream* d_input = nullptr;
  /** The name of the input file. */
  std::string d_infile_name;

  /** The log level. */
  uint64_t d_log_level;
  /** The verbosity level. */
  uint64_t d_verbosity;
  /** The associated logger class. */
  util::Logger d_logger;

  /** The output file stream if print to a file. */
  std::ofstream d_outfile;
  /** The output stream, either prints to d_outfile or std::cout. */
  std::ostream* d_out;

  /** The status of the input file set via set-info. */
  bitwuzla::Result d_status = bitwuzla::Result::UNKNOWN;
  /** The result of the last check-sat call. */
  bitwuzla::Result d_result = bitwuzla::Result::UNKNOWN;

  /**
   * True to automatically print the model after every sat query.
   * False (default) only prints the model after a `(get-model)` command for
   * SMT-LIB2 input, and does not print the model for BTOR2 input.
   */
  bool d_auto_print_model = false;

  /** True if parser is done parsing. */
  bool d_done = false;

  /** The error message in case of a parse error. */
  std::string d_error;
};
}  // namespace parser
}  // namespace bzla

#endif
