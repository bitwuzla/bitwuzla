#ifndef BZLA_PARSER_BTOR2_PARSER_H_INCLUDED
#define BZLA_PARSER_BTOR2_PARSER_H_INCLUDED

#include "parser/parser.h"

extern "C" {
#include "btor2parser/btor2parser.h"
}

namespace bzla {
namespace parser::btor2 {

class Parser : public bzla::parser::Parser
{
 public:
  /**
   * Constructor.
   * @param options The associated Bitwuzla options. Parser creates Bitwuzla
   *                instance from these options.
   * @param infile_name The name of the input file.
   */
  Parser(bitwuzla::Options& options, const std::string& infile_name);
  /**
   * Constructor.
   * @param options The associated Bitwuzla options. Parser creates Bitwuzla
   *                instance from these options.
   * @param infile_name The name of the input file.
   * @param infile      The input file.
   */
  Parser(bitwuzla::Options& options,
         const std::string& infile_name,
         FILE* infile);
  /** Destructor. */
  ~Parser();
  /**
   * Parse input file.
   * @param parse_only True to only parse without executing check-sat calls.
   */
  std::string parse(bool parse_only) override;

 private:
  Btor2Parser* d_btor2_parser = nullptr;

  void init();
  bitwuzla::Term bool_term_to_bv1(const bitwuzla::Term& term) const;
  bitwuzla::Term bv1_term_to_bool(const bitwuzla::Term& term) const;

  void error(const std::string& error_msg, int64_t line_id);

  bitwuzla::Term d_bv1_one;
  bitwuzla::Term d_bv1_zero;

  /** Parse statistics. */
  struct Statistics
  {
    Statistics();

    util::Statistics d_stats;
    /**
     * The time required for parsing.
     * @note This is not parse-only, it includes time for any calls to the
     *       solver (check-sat, get-model, ...).
     */
    util::TimerStatistic& time_parse;

  } d_statistics;
};
}  // namespace parser::btor2
}  // namespace bzla

#endif
