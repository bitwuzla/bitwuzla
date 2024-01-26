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
   * @param options     The associated Bitwuzla options. Parser creates
   *                    Bitwuzla instance from these options.
   * @param out         The output stream.
   */
  Parser(bitwuzla::Options& options, std::ostream* out = &std::cout)
      : d_options_orig(options),
        d_options(options),
        d_log_level(options.get(bitwuzla::Option::LOGLEVEL)),
        d_verbosity(options.get(bitwuzla::Option::VERBOSITY)),
        d_logger(d_log_level, d_verbosity),
        d_out(out)
  {
  }

  /** Destructor. */
  virtual ~Parser() {}

  /**
   * Parse input file.
   * @param infile_name The name of the input file.
   * @param parse_only  True to only parse without executing check-sat calls.
   * @return The error message, empty if no error.
   */
  virtual std::string parse(const std::string& infile_name,
                            bool parse_only) = 0;
  /**
   * Parse input file.
   * @param infile_name The name of the input file.
   * @param inpur       The input stream.
   * @param parse_only  True to only parse without executing check-sat calls.
   * @return The error message, empty if no error.
   */
  virtual std::string parse(const std::string& infile_name,
                            std::istream& input,
                            bool parse_only) = 0;

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
      d_bitwuzla.reset(new bitwuzla::Bitwuzla(d_options));
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
  /** The Bitwuzla instance. */
  std::shared_ptr<bitwuzla::Bitwuzla> d_bitwuzla;
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

  /** True if parser is done parsing. */
  bool d_done = false;

  /** The error message in case of a parse error. */
  std::string d_error;
};
}  // namespace parser
}  // namespace bzla

#endif
