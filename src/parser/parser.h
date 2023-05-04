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
   * @param infile_name The name of the input file. If name is <stdin> the
   *                    parser reads from stdin.
   */
  Parser(bitwuzla::Options& options, const std::string& infile_name)
      : d_options(options),
        d_infile_name(infile_name),
        d_log_level(options.get(bitwuzla::Option::LOGLEVEL)),
        d_verbosity(options.get(bitwuzla::Option::VERBOSITY)),
        d_logger(d_log_level, d_verbosity)
  {
    if (infile_name == "<stdin>")
    {
      d_infile = stdin;
    }
    else
    {
      d_infile             = std::fopen(infile_name.c_str(), "r");
      d_infile_needs_close = true;
    }
    if (!d_infile)
    {
      d_error = "failed to open '" + d_infile_name + "'";
    }
  }
  /**
   * Constructor.
   * @param options     The associated Bitwuzla options. Parser creates
   *                    Bitwuzla instance from these options.
   * @param infile_name The name of the input file.
   * @param infile      The input file.
   */
  Parser(bitwuzla::Options& options,
         const std::string& infile_name,
         FILE* infile)
      : d_options(options),
        d_infile_name(infile_name),
        d_infile(infile),
        d_log_level(options.get(bitwuzla::Option::LOGLEVEL)),
        d_verbosity(options.get(bitwuzla::Option::VERBOSITY)),
        d_logger(d_log_level, d_verbosity)
  {
    BITWUZLA_CHECK(infile != nullptr) << "expected non-null input file";
  }
  /** Destructor. */
  virtual ~Parser()
  {
    if (d_infile_needs_close && d_infile)
    {
      fclose(d_infile);
    }
  }

  /**
   * Parse input file.
   * @param parse_only True to only parse without executing check-sat calls.
   */
  virtual std::string parse(bool parse_only) = 0;
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
  bitwuzla::Bitwuzla* bitwuzla() { return d_bitwuzla.get(); }

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

  /** The Bitwuzla configuration options. */
  bitwuzla::Options& d_options;
  /** The Bitwuzla instance. */
  std::unique_ptr<bitwuzla::Bitwuzla> d_bitwuzla;
  /** The Bitwuzla terminator. */
  bitwuzla::Terminator* d_terminator = nullptr;

  /** The name of the input file. */
  const std::string& d_infile_name;
  /** The input file. */
  FILE* d_infile = nullptr;
  /** True if we need the input file on destruction. */
  bool d_infile_needs_close = false;

  /** The log level. */
  uint64_t d_log_level;
  /** The verbosity level. */
  uint64_t d_verbosity;
  /** The associated logger class. */
  util::Logger d_logger;

  /** The output file stream if print to a file. */
  std::ofstream d_outfile;
  /** The output stream, either prints to d_outfile or std::cout. */
  std::ostream* d_out = &std::cout;

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
